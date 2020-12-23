%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:38 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 122 expanded)
%              Number of leaves         :   45 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 205 expanded)
%              Number of equality atoms :   51 (  73 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_226,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_230,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_226])).

tff(c_70,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_231,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_70])).

tff(c_42,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_102,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_102])).

tff(c_108,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_105])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_109,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_113,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_109])).

tff(c_137,plain,(
    ! [B_74,A_75] :
      ( k7_relat_1(B_74,A_75) = B_74
      | ~ v4_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_140,plain,
    ( k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_137])).

tff(c_143,plain,(
    k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_140])).

tff(c_44,plain,(
    ! [B_24,A_23] :
      ( k2_relat_1(k7_relat_1(B_24,A_23)) = k9_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_147,plain,
    ( k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_44])).

tff(c_151,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_147])).

tff(c_40,plain,(
    ! [A_18,B_20] :
      ( k9_relat_1(A_18,k1_tarski(B_20)) = k11_relat_1(A_18,B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_156,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_40])).

tff(c_163,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_156])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_76,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_202,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_206,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_202])).

tff(c_304,plain,(
    ! [B_122,A_123,C_124] :
      ( k1_xboole_0 = B_122
      | k1_relset_1(A_123,B_122,C_124) = A_123
      | ~ v1_funct_2(C_124,A_123,B_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_307,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_304])).

tff(c_310,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_206,c_307])).

tff(c_311,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_310])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_172,plain,(
    ! [A_76,B_77,C_78] : k2_enumset1(A_76,A_76,B_77,C_78) = k1_enumset1(A_76,B_77,C_78) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [F_14,A_7,B_8,C_9] : r2_hidden(F_14,k2_enumset1(A_7,B_8,C_9,F_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_193,plain,(
    ! [C_79,A_80,B_81] : r2_hidden(C_79,k1_enumset1(A_80,B_81,C_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_10])).

tff(c_197,plain,(
    ! [B_82,A_83] : r2_hidden(B_82,k2_tarski(A_83,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_193])).

tff(c_200,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_197])).

tff(c_325,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_200])).

tff(c_48,plain,(
    ! [B_28,A_27] :
      ( k1_tarski(k1_funct_1(B_28,A_27)) = k11_relat_1(B_28,A_27)
      | ~ r2_hidden(A_27,k1_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_340,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_325,c_48])).

tff(c_343,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_78,c_163,c_340])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.36  
% 2.44/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.44/1.36  
% 2.44/1.36  %Foreground sorts:
% 2.44/1.36  
% 2.44/1.36  
% 2.44/1.36  %Background operators:
% 2.44/1.36  
% 2.44/1.36  
% 2.44/1.36  %Foreground operators:
% 2.44/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.44/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.44/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.44/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.44/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.44/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.44/1.36  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.44/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.44/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.44/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.44/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.44/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.44/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.44/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.44/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.44/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.36  
% 2.44/1.38  tff(f_125, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.44/1.38  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.44/1.38  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.44/1.38  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.44/1.38  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.44/1.38  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.44/1.38  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.44/1.38  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.44/1.38  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.44/1.38  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.44/1.38  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.44/1.38  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.44/1.38  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.44/1.38  tff(f_49, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.44/1.38  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 2.44/1.38  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.38  tff(c_226, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.44/1.38  tff(c_230, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_226])).
% 2.44/1.38  tff(c_70, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.38  tff(c_231, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_70])).
% 2.44/1.38  tff(c_42, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.44/1.38  tff(c_102, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.44/1.38  tff(c_105, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_102])).
% 2.44/1.38  tff(c_108, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_105])).
% 2.44/1.38  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.38  tff(c_109, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.38  tff(c_113, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_74, c_109])).
% 2.44/1.38  tff(c_137, plain, (![B_74, A_75]: (k7_relat_1(B_74, A_75)=B_74 | ~v4_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.44/1.38  tff(c_140, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_113, c_137])).
% 2.44/1.38  tff(c_143, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_140])).
% 2.44/1.38  tff(c_44, plain, (![B_24, A_23]: (k2_relat_1(k7_relat_1(B_24, A_23))=k9_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.44/1.38  tff(c_147, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_143, c_44])).
% 2.44/1.38  tff(c_151, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_147])).
% 2.44/1.38  tff(c_40, plain, (![A_18, B_20]: (k9_relat_1(A_18, k1_tarski(B_20))=k11_relat_1(A_18, B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.44/1.38  tff(c_156, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_151, c_40])).
% 2.44/1.38  tff(c_163, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_156])).
% 2.44/1.38  tff(c_72, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.38  tff(c_76, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.38  tff(c_202, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.44/1.38  tff(c_206, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_202])).
% 2.44/1.38  tff(c_304, plain, (![B_122, A_123, C_124]: (k1_xboole_0=B_122 | k1_relset_1(A_123, B_122, C_124)=A_123 | ~v1_funct_2(C_124, A_123, B_122) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.44/1.38  tff(c_307, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_74, c_304])).
% 2.44/1.38  tff(c_310, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_206, c_307])).
% 2.44/1.38  tff(c_311, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_310])).
% 2.44/1.38  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.44/1.38  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.44/1.38  tff(c_172, plain, (![A_76, B_77, C_78]: (k2_enumset1(A_76, A_76, B_77, C_78)=k1_enumset1(A_76, B_77, C_78))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.38  tff(c_10, plain, (![F_14, A_7, B_8, C_9]: (r2_hidden(F_14, k2_enumset1(A_7, B_8, C_9, F_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.44/1.38  tff(c_193, plain, (![C_79, A_80, B_81]: (r2_hidden(C_79, k1_enumset1(A_80, B_81, C_79)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_10])).
% 2.44/1.38  tff(c_197, plain, (![B_82, A_83]: (r2_hidden(B_82, k2_tarski(A_83, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_193])).
% 2.44/1.38  tff(c_200, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_197])).
% 2.44/1.38  tff(c_325, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_200])).
% 2.44/1.38  tff(c_48, plain, (![B_28, A_27]: (k1_tarski(k1_funct_1(B_28, A_27))=k11_relat_1(B_28, A_27) | ~r2_hidden(A_27, k1_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.44/1.38  tff(c_340, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_325, c_48])).
% 2.44/1.38  tff(c_343, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_78, c_163, c_340])).
% 2.44/1.38  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_343])).
% 2.44/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.38  
% 2.44/1.38  Inference rules
% 2.44/1.38  ----------------------
% 2.44/1.38  #Ref     : 0
% 2.44/1.38  #Sup     : 59
% 2.44/1.38  #Fact    : 0
% 2.44/1.38  #Define  : 0
% 2.44/1.38  #Split   : 0
% 2.44/1.38  #Chain   : 0
% 2.44/1.38  #Close   : 0
% 2.44/1.38  
% 2.44/1.38  Ordering : KBO
% 2.44/1.38  
% 2.44/1.38  Simplification rules
% 2.44/1.38  ----------------------
% 2.44/1.38  #Subsume      : 0
% 2.44/1.38  #Demod        : 23
% 2.44/1.38  #Tautology    : 36
% 2.44/1.38  #SimpNegUnit  : 2
% 2.44/1.38  #BackRed      : 8
% 2.44/1.38  
% 2.44/1.38  #Partial instantiations: 0
% 2.44/1.38  #Strategies tried      : 1
% 2.44/1.38  
% 2.44/1.38  Timing (in seconds)
% 2.44/1.38  ----------------------
% 2.44/1.38  Preprocessing        : 0.36
% 2.44/1.38  Parsing              : 0.19
% 2.44/1.38  CNF conversion       : 0.02
% 2.44/1.38  Main loop            : 0.23
% 2.44/1.38  Inferencing          : 0.08
% 2.44/1.38  Reduction            : 0.08
% 2.44/1.38  Demodulation         : 0.05
% 2.44/1.38  BG Simplification    : 0.02
% 2.44/1.38  Subsumption          : 0.05
% 2.44/1.38  Abstraction          : 0.01
% 2.44/1.38  MUC search           : 0.00
% 2.44/1.38  Cooper               : 0.00
% 2.44/1.38  Total                : 0.62
% 2.44/1.38  Index Insertion      : 0.00
% 2.44/1.38  Index Deletion       : 0.00
% 2.44/1.38  Index Matching       : 0.00
% 2.44/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
