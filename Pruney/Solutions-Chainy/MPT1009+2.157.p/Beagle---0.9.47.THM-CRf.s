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
% DateTime   : Thu Dec  3 10:15:04 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 125 expanded)
%              Number of leaves         :   40 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 231 expanded)
%              Number of equality atoms :   37 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_20,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_74,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_74])).

tff(c_80,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_77])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_163,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_167,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_163])).

tff(c_199,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_202,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_199])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_167,c_202])).

tff(c_206,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_205])).

tff(c_18,plain,(
    ! [A_14,B_16] :
      ( k9_relat_1(A_14,k1_tarski(B_16)) = k11_relat_1(A_14,B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_353,plain,(
    ! [A_89] :
      ( k9_relat_1(A_89,k1_relat_1('#skF_4')) = k11_relat_1(A_89,'#skF_1')
      | ~ v1_relat_1(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_18])).

tff(c_24,plain,(
    ! [A_21] :
      ( k9_relat_1(A_21,k1_relat_1(A_21)) = k2_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_360,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_24])).

tff(c_373,plain,(
    k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_360])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_82,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,k1_tarski(B_47)) = A_46
      | r2_hidden(B_47,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [B_8] : k4_xboole_0(k1_tarski(B_8),k1_tarski(B_8)) != k1_tarski(B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,(
    ! [B_47] : r2_hidden(B_47,k1_tarski(B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8])).

tff(c_226,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_98])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(k1_funct_1(B_23,A_22)) = k11_relat_1(B_23,A_22)
      | ~ r2_hidden(A_22,k1_relat_1(B_23))
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_247,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k11_relat_1('#skF_4','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_226,c_26])).

tff(c_250,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k11_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_52,c_247])).

tff(c_181,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k7_relset_1(A_66,B_67,C_68,D_69) = k9_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_184,plain,(
    ! [D_69] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_69) = k9_relat_1('#skF_4',D_69) ),
    inference(resolution,[status(thm)],[c_48,c_181])).

tff(c_44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_185,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_44])).

tff(c_290,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_185])).

tff(c_378,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_290])).

tff(c_392,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_378])).

tff(c_396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.37  
% 2.37/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.37  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.37  
% 2.37/1.37  %Foreground sorts:
% 2.37/1.37  
% 2.37/1.37  
% 2.37/1.37  %Background operators:
% 2.37/1.37  
% 2.37/1.37  
% 2.37/1.37  %Foreground operators:
% 2.37/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.37  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.37/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.37  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.37/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.37/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.37/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.37  
% 2.68/1.39  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.68/1.39  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.68/1.39  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.68/1.39  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.68/1.39  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.68/1.39  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.68/1.39  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.68/1.39  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.68/1.39  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.68/1.39  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.68/1.39  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.68/1.39  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.68/1.39  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.39  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.68/1.39  tff(c_74, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.39  tff(c_77, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_74])).
% 2.68/1.39  tff(c_80, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_77])).
% 2.68/1.39  tff(c_22, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.68/1.39  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.68/1.39  tff(c_50, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.68/1.39  tff(c_163, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.39  tff(c_167, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_163])).
% 2.68/1.39  tff(c_199, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.68/1.39  tff(c_202, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_48, c_199])).
% 2.68/1.39  tff(c_205, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_167, c_202])).
% 2.68/1.39  tff(c_206, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_205])).
% 2.68/1.39  tff(c_18, plain, (![A_14, B_16]: (k9_relat_1(A_14, k1_tarski(B_16))=k11_relat_1(A_14, B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.68/1.39  tff(c_353, plain, (![A_89]: (k9_relat_1(A_89, k1_relat_1('#skF_4'))=k11_relat_1(A_89, '#skF_1') | ~v1_relat_1(A_89))), inference(superposition, [status(thm), theory('equality')], [c_206, c_18])).
% 2.68/1.39  tff(c_24, plain, (![A_21]: (k9_relat_1(A_21, k1_relat_1(A_21))=k2_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.68/1.39  tff(c_360, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_353, c_24])).
% 2.68/1.39  tff(c_373, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_360])).
% 2.68/1.39  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.68/1.39  tff(c_82, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k1_tarski(B_47))=A_46 | r2_hidden(B_47, A_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.39  tff(c_8, plain, (![B_8]: (k4_xboole_0(k1_tarski(B_8), k1_tarski(B_8))!=k1_tarski(B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.68/1.39  tff(c_98, plain, (![B_47]: (r2_hidden(B_47, k1_tarski(B_47)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8])).
% 2.68/1.39  tff(c_226, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_98])).
% 2.68/1.39  tff(c_26, plain, (![B_23, A_22]: (k1_tarski(k1_funct_1(B_23, A_22))=k11_relat_1(B_23, A_22) | ~r2_hidden(A_22, k1_relat_1(B_23)) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.68/1.39  tff(c_247, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k11_relat_1('#skF_4', '#skF_1') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_226, c_26])).
% 2.68/1.39  tff(c_250, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k11_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_52, c_247])).
% 2.68/1.39  tff(c_181, plain, (![A_66, B_67, C_68, D_69]: (k7_relset_1(A_66, B_67, C_68, D_69)=k9_relat_1(C_68, D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.39  tff(c_184, plain, (![D_69]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_69)=k9_relat_1('#skF_4', D_69))), inference(resolution, [status(thm)], [c_48, c_181])).
% 2.68/1.39  tff(c_44, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.68/1.39  tff(c_185, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_44])).
% 2.68/1.39  tff(c_290, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_185])).
% 2.68/1.39  tff(c_378, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_290])).
% 2.68/1.39  tff(c_392, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_378])).
% 2.68/1.39  tff(c_396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_392])).
% 2.68/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  Inference rules
% 2.68/1.39  ----------------------
% 2.68/1.39  #Ref     : 0
% 2.68/1.39  #Sup     : 77
% 2.68/1.39  #Fact    : 0
% 2.68/1.39  #Define  : 0
% 2.68/1.39  #Split   : 0
% 2.68/1.39  #Chain   : 0
% 2.68/1.39  #Close   : 0
% 2.68/1.39  
% 2.68/1.39  Ordering : KBO
% 2.68/1.39  
% 2.68/1.39  Simplification rules
% 2.68/1.39  ----------------------
% 2.68/1.39  #Subsume      : 2
% 2.68/1.39  #Demod        : 39
% 2.68/1.39  #Tautology    : 45
% 2.68/1.39  #SimpNegUnit  : 3
% 2.68/1.39  #BackRed      : 9
% 2.68/1.39  
% 2.68/1.39  #Partial instantiations: 0
% 2.68/1.39  #Strategies tried      : 1
% 2.68/1.39  
% 2.68/1.39  Timing (in seconds)
% 2.68/1.39  ----------------------
% 2.68/1.39  Preprocessing        : 0.33
% 2.68/1.39  Parsing              : 0.18
% 2.68/1.39  CNF conversion       : 0.02
% 2.68/1.39  Main loop            : 0.24
% 2.68/1.39  Inferencing          : 0.10
% 2.68/1.39  Reduction            : 0.08
% 2.68/1.39  Demodulation         : 0.05
% 2.68/1.39  BG Simplification    : 0.02
% 2.68/1.39  Subsumption          : 0.04
% 2.68/1.39  Abstraction          : 0.01
% 2.68/1.39  MUC search           : 0.00
% 2.68/1.39  Cooper               : 0.00
% 2.68/1.39  Total                : 0.61
% 2.68/1.39  Index Insertion      : 0.00
% 2.68/1.39  Index Deletion       : 0.00
% 2.68/1.39  Index Matching       : 0.00
% 2.68/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
