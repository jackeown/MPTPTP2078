%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:52 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 116 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 273 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_74,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3657,plain,(
    ! [C_391,A_392,B_393] :
      ( m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393)))
      | ~ r1_tarski(k2_relat_1(C_391),B_393)
      | ~ r1_tarski(k1_relat_1(C_391),A_392)
      | ~ v1_relat_1(C_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_76,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68])).

tff(c_139,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_2453,plain,(
    ! [C_269,A_270,B_271] :
      ( m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ r1_tarski(k2_relat_1(C_269),B_271)
      | ~ r1_tarski(k1_relat_1(C_269),A_270)
      | ~ v1_relat_1(C_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2879,plain,(
    ! [C_318,A_319,B_320] :
      ( r1_tarski(C_318,k2_zfmisc_1(A_319,B_320))
      | ~ r1_tarski(k2_relat_1(C_318),B_320)
      | ~ r1_tarski(k1_relat_1(C_318),A_319)
      | ~ v1_relat_1(C_318) ) ),
    inference(resolution,[status(thm)],[c_2453,c_16])).

tff(c_2886,plain,(
    ! [A_319] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_319,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_319)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_70,c_2879])).

tff(c_2900,plain,(
    ! [A_321] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_321,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2886])).

tff(c_2910,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_2900])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2272,plain,(
    ! [A_253,B_254,C_255] :
      ( k1_relset_1(A_253,B_254,C_255) = k1_relat_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2287,plain,(
    ! [A_253,B_254,A_6] :
      ( k1_relset_1(A_253,B_254,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_253,B_254)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2272])).

tff(c_2922,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2910,c_2287])).

tff(c_2734,plain,(
    ! [B_300,C_301,A_302] :
      ( k1_xboole_0 = B_300
      | v1_funct_2(C_301,A_302,B_300)
      | k1_relset_1(A_302,B_300,C_301) != A_302
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_302,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2929,plain,(
    ! [B_322,A_323,A_324] :
      ( k1_xboole_0 = B_322
      | v1_funct_2(A_323,A_324,B_322)
      | k1_relset_1(A_324,B_322,A_323) != A_324
      | ~ r1_tarski(A_323,k2_zfmisc_1(A_324,B_322)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2734])).

tff(c_2932,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2910,c_2929])).

tff(c_2956,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_2932])).

tff(c_2969,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_2956])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_129,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_137,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_129])).

tff(c_3001,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2969,c_137])).

tff(c_160,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_160])).

tff(c_213,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_3018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3001,c_213])).

tff(c_3019,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_3128,plain,(
    ! [A_337] :
      ( v1_funct_2(A_337,k1_relat_1(A_337),k2_relat_1(A_337))
      | ~ v1_funct_1(A_337)
      | ~ v1_relat_1(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3131,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3019,c_3128])).

tff(c_3148,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3131])).

tff(c_3150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_3148])).

tff(c_3151,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3671,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3657,c_3151])).

tff(c_3690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6,c_70,c_3671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/2.03  
% 4.94/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/2.04  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.94/2.04  
% 4.94/2.04  %Foreground sorts:
% 4.94/2.04  
% 4.94/2.04  
% 4.94/2.04  %Background operators:
% 4.94/2.04  
% 4.94/2.04  
% 4.94/2.04  %Foreground operators:
% 4.94/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.94/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.94/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.94/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.94/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.94/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.94/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.94/2.04  tff('#skF_2', type, '#skF_2': $i).
% 4.94/2.04  tff('#skF_3', type, '#skF_3': $i).
% 4.94/2.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.94/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.94/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.94/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.94/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.94/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.94/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.94/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.94/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.94/2.04  
% 4.94/2.05  tff(f_135, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.94/2.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.94/2.05  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.94/2.05  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.94/2.05  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.94/2.05  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.94/2.05  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.94/2.05  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.94/2.05  tff(c_74, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.94/2.05  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.94/2.05  tff(c_70, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.94/2.05  tff(c_3657, plain, (![C_391, A_392, B_393]: (m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))) | ~r1_tarski(k2_relat_1(C_391), B_393) | ~r1_tarski(k1_relat_1(C_391), A_392) | ~v1_relat_1(C_391))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.94/2.05  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.94/2.05  tff(c_68, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.94/2.05  tff(c_76, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68])).
% 4.94/2.05  tff(c_139, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_76])).
% 4.94/2.05  tff(c_2453, plain, (![C_269, A_270, B_271]: (m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~r1_tarski(k2_relat_1(C_269), B_271) | ~r1_tarski(k1_relat_1(C_269), A_270) | ~v1_relat_1(C_269))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.94/2.05  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.94/2.05  tff(c_2879, plain, (![C_318, A_319, B_320]: (r1_tarski(C_318, k2_zfmisc_1(A_319, B_320)) | ~r1_tarski(k2_relat_1(C_318), B_320) | ~r1_tarski(k1_relat_1(C_318), A_319) | ~v1_relat_1(C_318))), inference(resolution, [status(thm)], [c_2453, c_16])).
% 4.94/2.05  tff(c_2886, plain, (![A_319]: (r1_tarski('#skF_3', k2_zfmisc_1(A_319, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_319) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_2879])).
% 4.94/2.05  tff(c_2900, plain, (![A_321]: (r1_tarski('#skF_3', k2_zfmisc_1(A_321, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_321))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2886])).
% 4.94/2.05  tff(c_2910, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_2900])).
% 4.94/2.05  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.94/2.05  tff(c_2272, plain, (![A_253, B_254, C_255]: (k1_relset_1(A_253, B_254, C_255)=k1_relat_1(C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.94/2.05  tff(c_2287, plain, (![A_253, B_254, A_6]: (k1_relset_1(A_253, B_254, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_253, B_254)))), inference(resolution, [status(thm)], [c_18, c_2272])).
% 4.94/2.05  tff(c_2922, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2910, c_2287])).
% 4.94/2.05  tff(c_2734, plain, (![B_300, C_301, A_302]: (k1_xboole_0=B_300 | v1_funct_2(C_301, A_302, B_300) | k1_relset_1(A_302, B_300, C_301)!=A_302 | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_302, B_300))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.94/2.05  tff(c_2929, plain, (![B_322, A_323, A_324]: (k1_xboole_0=B_322 | v1_funct_2(A_323, A_324, B_322) | k1_relset_1(A_324, B_322, A_323)!=A_324 | ~r1_tarski(A_323, k2_zfmisc_1(A_324, B_322)))), inference(resolution, [status(thm)], [c_18, c_2734])).
% 4.94/2.05  tff(c_2932, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2910, c_2929])).
% 4.94/2.05  tff(c_2956, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_139, c_2932])).
% 4.94/2.05  tff(c_2969, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_2956])).
% 4.94/2.05  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.94/2.05  tff(c_129, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.94/2.05  tff(c_137, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_129])).
% 4.94/2.05  tff(c_3001, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2969, c_137])).
% 4.94/2.05  tff(c_160, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.94/2.05  tff(c_171, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_160])).
% 4.94/2.05  tff(c_213, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_171])).
% 4.94/2.05  tff(c_3018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3001, c_213])).
% 4.94/2.05  tff(c_3019, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_171])).
% 4.94/2.05  tff(c_3128, plain, (![A_337]: (v1_funct_2(A_337, k1_relat_1(A_337), k2_relat_1(A_337)) | ~v1_funct_1(A_337) | ~v1_relat_1(A_337))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.94/2.05  tff(c_3131, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3019, c_3128])).
% 4.94/2.05  tff(c_3148, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3131])).
% 4.94/2.05  tff(c_3150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_3148])).
% 4.94/2.05  tff(c_3151, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_76])).
% 4.94/2.05  tff(c_3671, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3657, c_3151])).
% 4.94/2.05  tff(c_3690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_6, c_70, c_3671])).
% 4.94/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/2.05  
% 4.94/2.05  Inference rules
% 4.94/2.05  ----------------------
% 4.94/2.05  #Ref     : 0
% 4.94/2.05  #Sup     : 712
% 4.94/2.05  #Fact    : 0
% 4.94/2.05  #Define  : 0
% 4.94/2.05  #Split   : 15
% 4.94/2.05  #Chain   : 0
% 4.94/2.05  #Close   : 0
% 4.94/2.05  
% 4.94/2.05  Ordering : KBO
% 4.94/2.05  
% 4.94/2.05  Simplification rules
% 4.94/2.05  ----------------------
% 4.94/2.05  #Subsume      : 72
% 4.94/2.05  #Demod        : 1002
% 4.94/2.05  #Tautology    : 420
% 4.94/2.05  #SimpNegUnit  : 7
% 4.94/2.05  #BackRed      : 171
% 4.94/2.05  
% 4.94/2.05  #Partial instantiations: 0
% 4.94/2.05  #Strategies tried      : 1
% 4.94/2.05  
% 4.94/2.05  Timing (in seconds)
% 4.94/2.05  ----------------------
% 4.94/2.05  Preprocessing        : 0.36
% 4.94/2.05  Parsing              : 0.19
% 4.94/2.05  CNF conversion       : 0.02
% 4.94/2.05  Main loop            : 0.80
% 4.94/2.05  Inferencing          : 0.27
% 4.94/2.05  Reduction            : 0.26
% 4.94/2.05  Demodulation         : 0.19
% 4.94/2.05  BG Simplification    : 0.04
% 4.94/2.05  Subsumption          : 0.16
% 4.94/2.05  Abstraction          : 0.04
% 4.94/2.05  MUC search           : 0.00
% 4.94/2.05  Cooper               : 0.00
% 4.94/2.05  Total                : 1.19
% 4.94/2.05  Index Insertion      : 0.00
% 4.94/2.05  Index Deletion       : 0.00
% 4.94/2.05  Index Matching       : 0.00
% 4.94/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
