%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:41 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 178 expanded)
%              Number of leaves         :   39 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 366 expanded)
%              Number of equality atoms :   60 ( 140 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_16,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_75,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_75])).

tff(c_81,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_78])).

tff(c_82,plain,(
    ! [A_39] :
      ( k1_relat_1(A_39) = k1_xboole_0
      | k2_relat_1(A_39) != k1_xboole_0
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_89,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_82])).

tff(c_91,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_155,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_159,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_155])).

tff(c_197,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_xboole_0 = B_72
      | k1_relset_1(A_73,B_72,C_74) = A_73
      | ~ v1_funct_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_200,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_197])).

tff(c_203,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_159,c_200])).

tff(c_204,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_203])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( k9_relat_1(A_11,k1_tarski(B_13)) = k11_relat_1(A_11,B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_258,plain,(
    ! [A_78] :
      ( k9_relat_1(A_78,k1_relat_1('#skF_3')) = k11_relat_1(A_78,'#skF_1')
      | ~ v1_relat_1(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_14])).

tff(c_18,plain,(
    ! [A_16] :
      ( k9_relat_1(A_16,k1_relat_1(A_16)) = k2_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_265,plain,
    ( k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_18])).

tff(c_275,plain,(
    k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_81,c_265])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,k1_relat_1(B_18))
      | k11_relat_1(B_18,A_17) = k1_xboole_0
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_173,plain,(
    ! [B_68,A_69] :
      ( k1_tarski(k1_funct_1(B_68,A_69)) = k11_relat_1(B_68,A_69)
      | ~ r2_hidden(A_69,k1_relat_1(B_68))
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_178,plain,(
    ! [B_70,A_71] :
      ( k1_tarski(k1_funct_1(B_70,A_71)) = k11_relat_1(B_70,A_71)
      | ~ v1_funct_1(B_70)
      | k11_relat_1(B_70,A_71) = k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_20,c_173])).

tff(c_150,plain,(
    ! [A_55,B_56,C_57] :
      ( k2_relset_1(A_55,B_56,C_57) = k2_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_154,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_150])).

tff(c_46,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_160,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_46])).

tff(c_184,plain,
    ( k11_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | k11_relat_1('#skF_3','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_160])).

tff(c_195,plain,
    ( k11_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3')
    | k11_relat_1('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_184])).

tff(c_285,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_275,c_195])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_285])).

tff(c_287,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_391,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_394,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_391])).

tff(c_396,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_394])).

tff(c_433,plain,(
    ! [B_113,A_114,C_115] :
      ( k1_xboole_0 = B_113
      | k1_relset_1(A_114,B_113,C_115) = A_114
      | ~ v1_funct_2(C_115,A_114,B_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_436,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_433])).

tff(c_439,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_396,c_436])).

tff(c_440,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_439])).

tff(c_10,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_450,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_10])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:36:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.37  
% 2.34/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.37  
% 2.61/1.37  %Foreground sorts:
% 2.61/1.37  
% 2.61/1.37  
% 2.61/1.37  %Background operators:
% 2.61/1.37  
% 2.61/1.37  
% 2.61/1.37  %Foreground operators:
% 2.61/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.61/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.61/1.37  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.61/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.61/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.61/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.61/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.37  
% 2.61/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.61/1.39  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.61/1.39  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.61/1.39  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.61/1.39  tff(f_66, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.61/1.39  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.61/1.39  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.61/1.39  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.61/1.39  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.61/1.39  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.61/1.39  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.61/1.39  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.61/1.39  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.61/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.61/1.39  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.61/1.39  tff(c_52, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.61/1.39  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.39  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.61/1.39  tff(c_75, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.39  tff(c_78, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_75])).
% 2.61/1.39  tff(c_81, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_78])).
% 2.61/1.39  tff(c_82, plain, (![A_39]: (k1_relat_1(A_39)=k1_xboole_0 | k2_relat_1(A_39)!=k1_xboole_0 | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.61/1.39  tff(c_89, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_81, c_82])).
% 2.61/1.39  tff(c_91, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_89])).
% 2.61/1.39  tff(c_155, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.39  tff(c_159, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_155])).
% 2.61/1.39  tff(c_197, plain, (![B_72, A_73, C_74]: (k1_xboole_0=B_72 | k1_relset_1(A_73, B_72, C_74)=A_73 | ~v1_funct_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.61/1.39  tff(c_200, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_50, c_197])).
% 2.61/1.39  tff(c_203, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_159, c_200])).
% 2.61/1.39  tff(c_204, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_203])).
% 2.61/1.39  tff(c_14, plain, (![A_11, B_13]: (k9_relat_1(A_11, k1_tarski(B_13))=k11_relat_1(A_11, B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.39  tff(c_258, plain, (![A_78]: (k9_relat_1(A_78, k1_relat_1('#skF_3'))=k11_relat_1(A_78, '#skF_1') | ~v1_relat_1(A_78))), inference(superposition, [status(thm), theory('equality')], [c_204, c_14])).
% 2.61/1.39  tff(c_18, plain, (![A_16]: (k9_relat_1(A_16, k1_relat_1(A_16))=k2_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.39  tff(c_265, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_258, c_18])).
% 2.61/1.39  tff(c_275, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_81, c_265])).
% 2.61/1.39  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.61/1.39  tff(c_20, plain, (![A_17, B_18]: (r2_hidden(A_17, k1_relat_1(B_18)) | k11_relat_1(B_18, A_17)=k1_xboole_0 | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.39  tff(c_173, plain, (![B_68, A_69]: (k1_tarski(k1_funct_1(B_68, A_69))=k11_relat_1(B_68, A_69) | ~r2_hidden(A_69, k1_relat_1(B_68)) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.39  tff(c_178, plain, (![B_70, A_71]: (k1_tarski(k1_funct_1(B_70, A_71))=k11_relat_1(B_70, A_71) | ~v1_funct_1(B_70) | k11_relat_1(B_70, A_71)=k1_xboole_0 | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_20, c_173])).
% 2.61/1.39  tff(c_150, plain, (![A_55, B_56, C_57]: (k2_relset_1(A_55, B_56, C_57)=k2_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.61/1.39  tff(c_154, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_150])).
% 2.61/1.39  tff(c_46, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.61/1.39  tff(c_160, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_46])).
% 2.61/1.39  tff(c_184, plain, (k11_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | k11_relat_1('#skF_3', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_160])).
% 2.61/1.39  tff(c_195, plain, (k11_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3') | k11_relat_1('#skF_3', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_184])).
% 2.61/1.39  tff(c_285, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_275, c_275, c_195])).
% 2.61/1.39  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_285])).
% 2.61/1.39  tff(c_287, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_89])).
% 2.61/1.39  tff(c_391, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.39  tff(c_394, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_391])).
% 2.61/1.39  tff(c_396, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_287, c_394])).
% 2.61/1.39  tff(c_433, plain, (![B_113, A_114, C_115]: (k1_xboole_0=B_113 | k1_relset_1(A_114, B_113, C_115)=A_114 | ~v1_funct_2(C_115, A_114, B_113) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.61/1.39  tff(c_436, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_50, c_433])).
% 2.61/1.39  tff(c_439, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_396, c_436])).
% 2.61/1.39  tff(c_440, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_439])).
% 2.61/1.39  tff(c_10, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.39  tff(c_450, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_440, c_10])).
% 2.61/1.39  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_450])).
% 2.61/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  Inference rules
% 2.61/1.39  ----------------------
% 2.61/1.39  #Ref     : 0
% 2.61/1.39  #Sup     : 91
% 2.61/1.39  #Fact    : 0
% 2.61/1.39  #Define  : 0
% 2.61/1.39  #Split   : 1
% 2.61/1.39  #Chain   : 0
% 2.61/1.39  #Close   : 0
% 2.61/1.39  
% 2.61/1.39  Ordering : KBO
% 2.61/1.39  
% 2.61/1.39  Simplification rules
% 2.61/1.39  ----------------------
% 2.61/1.39  #Subsume      : 1
% 2.61/1.39  #Demod        : 43
% 2.61/1.39  #Tautology    : 61
% 2.61/1.39  #SimpNegUnit  : 6
% 2.61/1.39  #BackRed      : 10
% 2.61/1.39  
% 2.61/1.39  #Partial instantiations: 0
% 2.61/1.39  #Strategies tried      : 1
% 2.61/1.39  
% 2.61/1.39  Timing (in seconds)
% 2.61/1.39  ----------------------
% 2.61/1.39  Preprocessing        : 0.33
% 2.61/1.39  Parsing              : 0.18
% 2.61/1.39  CNF conversion       : 0.02
% 2.61/1.39  Main loop            : 0.24
% 2.61/1.39  Inferencing          : 0.10
% 2.61/1.39  Reduction            : 0.07
% 2.61/1.39  Demodulation         : 0.05
% 2.61/1.39  BG Simplification    : 0.02
% 2.61/1.39  Subsumption          : 0.04
% 2.61/1.39  Abstraction          : 0.01
% 2.61/1.39  MUC search           : 0.00
% 2.61/1.39  Cooper               : 0.00
% 2.61/1.39  Total                : 0.61
% 2.61/1.39  Index Insertion      : 0.00
% 2.61/1.39  Index Deletion       : 0.00
% 2.61/1.39  Index Matching       : 0.00
% 2.61/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
