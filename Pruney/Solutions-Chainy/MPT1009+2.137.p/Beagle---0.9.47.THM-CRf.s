%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:01 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 176 expanded)
%              Number of leaves         :   45 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 333 expanded)
%              Number of equality atoms :   46 (  86 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_121,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

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

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_20,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_79,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_79])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_82])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_222,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_226,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_222])).

tff(c_263,plain,(
    ! [B_96,A_97,C_98] :
      ( k1_xboole_0 = B_96
      | k1_relset_1(A_97,B_96,C_98) = A_97
      | ~ v1_funct_2(C_98,A_97,B_96)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_266,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_263])).

tff(c_269,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_226,c_266])).

tff(c_270,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_269])).

tff(c_163,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_167,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_163])).

tff(c_275,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_167])).

tff(c_26,plain,(
    ! [B_24,A_23] :
      ( k7_relat_1(B_24,A_23) = B_24
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_314,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_275,c_26])).

tff(c_317,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_314])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_327,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_24])).

tff(c_331,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_327])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k9_relat_1(B_20,k1_relat_1(B_20)))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_386,plain,(
    ! [A_19] :
      ( r1_tarski(k9_relat_1('#skF_4',A_19),k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_22])).

tff(c_394,plain,(
    ! [A_19] : r1_tarski(k9_relat_1('#skF_4',A_19),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_386])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_170,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_26])).

tff(c_173,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_170])).

tff(c_177,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_24])).

tff(c_181,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_177])).

tff(c_18,plain,(
    ! [A_14,B_16] :
      ( k9_relat_1(A_14,k1_tarski(B_16)) = k11_relat_1(A_14,B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_192,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_18])).

tff(c_199,plain,(
    k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_192])).

tff(c_86,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,k1_tarski(B_49)) = A_48
      | r2_hidden(B_49,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [B_8] : k4_xboole_0(k1_tarski(B_8),k1_tarski(B_8)) != k1_tarski(B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,(
    ! [B_49] : r2_hidden(B_49,k1_tarski(B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8])).

tff(c_296,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_98])).

tff(c_28,plain,(
    ! [B_26,A_25] :
      ( k1_tarski(k1_funct_1(B_26,A_25)) = k11_relat_1(B_26,A_25)
      | ~ r2_hidden(A_25,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_320,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k11_relat_1('#skF_4','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_296,c_28])).

tff(c_323,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_199,c_320])).

tff(c_239,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k7_relset_1(A_82,B_83,C_84,D_85) = k9_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_242,plain,(
    ! [D_85] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_85) = k9_relat_1('#skF_4',D_85) ),
    inference(resolution,[status(thm)],[c_54,c_239])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_243,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_50])).

tff(c_402,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_243])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:18:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.39  
% 2.70/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.70/1.40  
% 2.70/1.40  %Foreground sorts:
% 2.70/1.40  
% 2.70/1.40  
% 2.70/1.40  %Background operators:
% 2.70/1.40  
% 2.70/1.40  
% 2.70/1.40  %Foreground operators:
% 2.70/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.70/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.70/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.40  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.70/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.70/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.70/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.70/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.70/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.40  
% 2.70/1.41  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.70/1.41  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.70/1.41  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.70/1.41  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.70/1.41  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.70/1.41  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.70/1.41  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.70/1.41  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.70/1.41  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 2.70/1.41  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.70/1.41  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.70/1.41  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.70/1.41  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.70/1.41  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.70/1.41  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.41  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.70/1.41  tff(c_79, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.41  tff(c_82, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_79])).
% 2.70/1.41  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_82])).
% 2.70/1.41  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.70/1.41  tff(c_56, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.70/1.41  tff(c_222, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.41  tff(c_226, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_222])).
% 2.70/1.41  tff(c_263, plain, (![B_96, A_97, C_98]: (k1_xboole_0=B_96 | k1_relset_1(A_97, B_96, C_98)=A_97 | ~v1_funct_2(C_98, A_97, B_96) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.70/1.41  tff(c_266, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_54, c_263])).
% 2.70/1.41  tff(c_269, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_226, c_266])).
% 2.70/1.41  tff(c_270, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_269])).
% 2.70/1.41  tff(c_163, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.41  tff(c_167, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_163])).
% 2.70/1.41  tff(c_275, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_167])).
% 2.70/1.41  tff(c_26, plain, (![B_24, A_23]: (k7_relat_1(B_24, A_23)=B_24 | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.70/1.41  tff(c_314, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_275, c_26])).
% 2.70/1.41  tff(c_317, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_314])).
% 2.70/1.41  tff(c_24, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.41  tff(c_327, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_317, c_24])).
% 2.70/1.41  tff(c_331, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_327])).
% 2.70/1.41  tff(c_22, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k9_relat_1(B_20, k1_relat_1(B_20))) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.70/1.41  tff(c_386, plain, (![A_19]: (r1_tarski(k9_relat_1('#skF_4', A_19), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_331, c_22])).
% 2.70/1.41  tff(c_394, plain, (![A_19]: (r1_tarski(k9_relat_1('#skF_4', A_19), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_386])).
% 2.70/1.41  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.70/1.41  tff(c_170, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_167, c_26])).
% 2.70/1.41  tff(c_173, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_170])).
% 2.70/1.41  tff(c_177, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_173, c_24])).
% 2.70/1.41  tff(c_181, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_177])).
% 2.70/1.41  tff(c_18, plain, (![A_14, B_16]: (k9_relat_1(A_14, k1_tarski(B_16))=k11_relat_1(A_14, B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.70/1.41  tff(c_192, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_181, c_18])).
% 2.70/1.41  tff(c_199, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_192])).
% 2.70/1.41  tff(c_86, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k1_tarski(B_49))=A_48 | r2_hidden(B_49, A_48))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.41  tff(c_8, plain, (![B_8]: (k4_xboole_0(k1_tarski(B_8), k1_tarski(B_8))!=k1_tarski(B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.70/1.41  tff(c_98, plain, (![B_49]: (r2_hidden(B_49, k1_tarski(B_49)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_8])).
% 2.70/1.41  tff(c_296, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_98])).
% 2.70/1.41  tff(c_28, plain, (![B_26, A_25]: (k1_tarski(k1_funct_1(B_26, A_25))=k11_relat_1(B_26, A_25) | ~r2_hidden(A_25, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.41  tff(c_320, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k11_relat_1('#skF_4', '#skF_1') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_296, c_28])).
% 2.70/1.41  tff(c_323, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_199, c_320])).
% 2.70/1.41  tff(c_239, plain, (![A_82, B_83, C_84, D_85]: (k7_relset_1(A_82, B_83, C_84, D_85)=k9_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.41  tff(c_242, plain, (![D_85]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_85)=k9_relat_1('#skF_4', D_85))), inference(resolution, [status(thm)], [c_54, c_239])).
% 2.70/1.41  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.70/1.41  tff(c_243, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_50])).
% 2.70/1.41  tff(c_402, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_243])).
% 2.70/1.41  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_394, c_402])).
% 2.70/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.41  
% 2.70/1.41  Inference rules
% 2.70/1.41  ----------------------
% 2.70/1.41  #Ref     : 0
% 2.70/1.41  #Sup     : 90
% 2.70/1.41  #Fact    : 0
% 2.70/1.41  #Define  : 0
% 2.70/1.41  #Split   : 0
% 2.70/1.41  #Chain   : 0
% 2.70/1.41  #Close   : 0
% 2.70/1.41  
% 2.70/1.41  Ordering : KBO
% 2.70/1.41  
% 2.70/1.41  Simplification rules
% 2.70/1.41  ----------------------
% 2.70/1.41  #Subsume      : 0
% 2.70/1.41  #Demod        : 58
% 2.70/1.41  #Tautology    : 53
% 2.70/1.41  #SimpNegUnit  : 4
% 2.70/1.41  #BackRed      : 10
% 2.70/1.41  
% 2.70/1.41  #Partial instantiations: 0
% 2.70/1.41  #Strategies tried      : 1
% 2.70/1.41  
% 2.70/1.41  Timing (in seconds)
% 2.70/1.41  ----------------------
% 2.70/1.42  Preprocessing        : 0.36
% 2.70/1.42  Parsing              : 0.20
% 2.70/1.42  CNF conversion       : 0.02
% 2.70/1.42  Main loop            : 0.24
% 2.70/1.42  Inferencing          : 0.09
% 2.70/1.42  Reduction            : 0.08
% 2.70/1.42  Demodulation         : 0.06
% 2.70/1.42  BG Simplification    : 0.02
% 2.70/1.42  Subsumption          : 0.03
% 2.70/1.42  Abstraction          : 0.01
% 2.70/1.42  MUC search           : 0.00
% 2.70/1.42  Cooper               : 0.00
% 2.70/1.42  Total                : 0.63
% 2.70/1.42  Index Insertion      : 0.00
% 2.70/1.42  Index Deletion       : 0.00
% 2.70/1.42  Index Matching       : 0.00
% 2.70/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
